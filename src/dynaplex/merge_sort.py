#!/usr/bin/env python3

import random
import os

counter = 0

def random_list(size):
    list = []
    for i in range(size):
        list.append(random.randint(-10000, 10000))
    return list


def merge_sort(myList, depth, file):

    with open(file, 'a') as f:
        print("{};{}".format(depth, len(myList)), file=f)
    if len(myList) > 1:

        mid = len(myList) // 2
        left = myList[:mid]
        right = myList[mid:]

        # Recursive call on each half
        merge_sort(left, depth+1, file)
        merge_sort(right, depth+1, file)

        # Two iterators for traversing the two halves
        i = 0
        j = 0

        # Iterator for the main list
        k = 0

        while i < len(left) and j < len(right):
            if depth==0:
                global counter
                counter = counter + 1
            if left[i] < right[j]:
              # The value from the left half has been used
              myList[k] = left[i]
              # Move the iterator forward
              i += 1
            else:
                myList[k] = right[j]
                j += 1
            # Move to the next slot
            k += 1

        # For all the remaining values
        while i < len(left):
            if depth==0:
                counter = counter + 1
            myList[k] = left[i]
            i += 1
            k += 1

        while j < len(right):
            if depth==0:
                counter = counter + 1
            myList[k]=right[j]
            j += 1
            k += 1
    return

# Driver collect traces
def main():
    global counter
    counter = 0
    size = random.randint(1, 500)
    arr = random_list(size)
    depth = 0
    path = "./merge_sort"
    try:
       os.mkdir(path)
    except OSError as error:
       pass
    file = "./merge_sort/output-{}".format(size)
    merge_sort(arr, depth, file)
    with open("./merge_sort/traces", 'a') as f:
       print("{};{}".format(size, counter), file=f)
    counter = 0

if __name__ == '__main__':
    for i in range(100):
       main()
    #main()
