object InsertSort {

  def insertionSort(list: List[Int]): List[Int] = {

    // helper function
    def insert(x: Int, sorted: List[Int]): List[Int] = sorted match {
      case Nil => List(x)
      case head :: tail if x <= head => x :: sorted
      case head :: tail => head :: insert(x, tail)
    }

    list.foldLeft(List.empty[Int])((sorted, x) => insert(x, sorted))
  }

  def main(args: Array[String]) = {
    val list = List(4, 10, 122, 943, 1, -100, -234)

    println(s"Unsorted list: $list")

    println(s"Sorted list: ${insertionSort(list)}")
  }
}
